// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
//! The purpose of this module is to provide abstractions for working with
//! metrics in the context of rust-vmm components where there is a strong need
//! to have metrics as an optional feature.
//!
//! As multiple stakeholders are using these components, there are also
//! questions regarding the serialization format, as metrics are expected to be
//! flexible enough to allow different formatting, serialization and writers.
//! When using the rust-vmm metrics, the expectation is that VMMs built on top
//! of these components can choose what metrics they’re interested in and also
//! can add their own custom metrics without the need to maintain forks.

use std::sync::atomic::{AtomicU64, Ordering};

/// Abstraction over the common metric operations.
///
/// An object implementing `Metric` is expected to have an inner counter that
/// can be incremented and reset. The `Metric` trait can be used for
/// implementing a metric system backend (or an aggregator).
pub trait Metric {
    /// Adds `value` to the current counter.
    fn add(&self, value: u64);
    /// Increments by 1 unit the current counter.
    fn inc(&self) {
        self.add(1);
    }
    /// Returns current value of the counter.
    fn count(&self) -> u64;
    /// Resets the metric counter.
    fn reset(&self);
    /// Set the metric counter `value`.
    fn set(&self, value: u64);
}

impl Metric for AtomicU64 {
    /// Adds `value` to the current counter.
    fn add(&self, value: u64) {
        self.fetch_add(value, Ordering::Relaxed);
    }

    /// Returns current value of the counter.
    fn count(&self) -> u64 {
        self.load(Ordering::Relaxed)
    }

    /// Resets the metric counter to 0.
    fn reset(&self) {
        self.store(0, Ordering::Relaxed)
    }

    /// Set the metric counter `value`.
    fn set(&self, value: u64) {
        self.store(value, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use crate::metric::Metric;

    use std::sync::atomic::AtomicU64;
    use std::sync::Arc;

    struct Dog<T: DogEvents> {
        metrics: T,
    }

    // Trait that declares events that can happen during the lifetime of the
    // `Dog` which should also have associated events (such as metrics).
    trait DogEvents {
        // Event to be called when the dog `bark`s.
        fn inc_bark(&self);
        // Event to be called when the dog `eat`s.
        fn inc_eat(&self);
    }

    impl<T: DogEvents> Dog<T> {
        fn bark(&self) {
            println!("bark! bark!");
            self.metrics.inc_bark();
        }

        fn eat(&self) {
            println!("nom! nom!");
            self.metrics.inc_eat();
        }
    }

    impl<T: DogEvents> Dog<T> {
        fn new_with_metrics(metrics: T) -> Self {
            Self { metrics }
        }
    }

    #[test]
    fn test_main() {
        // The `Metric` trait is implemented for `AtomicUsize` so we can easily use it as the
        // counter for the dog events.
        #[derive(Default, Debug)]
        struct DogEventMetrics {
            bark: AtomicU64,
            eat: AtomicU64,
        }

        impl DogEvents for Arc<DogEventMetrics> {
            fn inc_bark(&self) {
                self.bark.inc();
            }

            fn inc_eat(&self) {
                self.eat.inc();
            }
        }

        // This is the central object of mini-app built in this example.
        // All the metrics that might be needed by the app are referenced through the
        // `SystemMetrics` object. The `SystemMetric` also decides how to format the metrics.
        // In this simple example, the metrics are formatted with the dummy Debug formatter.
        #[derive(Default)]
        struct SystemMetrics {
            pub(crate) dog_metrics: Arc<DogEventMetrics>,
        }

        impl SystemMetrics {
            fn serialize(&self) -> String {
                let mut serialized_metrics = format!("{:#?}", &self.dog_metrics);
                serialized_metrics.retain(|c| !c.is_whitespace());
                serialized_metrics
            }
        }

        let system_metrics = SystemMetrics::default();
        let dog = Dog::new_with_metrics(system_metrics.dog_metrics.clone());
        dog.bark();
        dog.bark();
        dog.eat();

        let expected_metrics = String::from("DogEventMetrics{bark:2,eat:1,}");
        let actual_metrics = system_metrics.serialize();
        assert_eq!(expected_metrics, actual_metrics);
    }
}
