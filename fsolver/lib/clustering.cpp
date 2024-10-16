#include "clustering.h"
#include <iostream>
#include <vector>
#include <cmath>
#include <limits>
#include <cstdlib>
#include <ctime>
#include <algorithm>

double euclideanDistance(const oracle_point& a, const oracle_point& b) {
    double sum = 0.0;
    for (int i = 0; i < a.args.size(); ++i) {
        // in case overflow
        sum += ((double)(a.args[i]) - (double)(b.args[i])) * ((double)(a.args[i]) - (double)(b.args[i]));
    }
    return std::sqrt(sum);
}

double euclideanDistanceToCentroid(const oracle_point& a, const std::vector<double>& b) {
    double sum = 0.0;
    for (int i = 0; i < a.args.size(); ++i) {
        // in case overflow
        sum += ((double)(a.args[i]) - b[i]) * ((double)(a.args[i]) - b[i]);
    }
    return std::sqrt(sum);
}

double euclideanDistanceBetweenCentroids(const std::vector<double>& a, const std::vector<double>& b) {
    double sum = 0.0;
    for (int i = 0; i < a.size(); ++i) {
        // in case overflow
        sum += (a[i] - b[i]) * (a[i] - b[i]);
    }
    return std::sqrt(sum);
}

void initializeCentroids(std::vector<std::vector<double>>& centroids, std::vector<oracle_point>& points, int k) {
    std::sort(points.begin(), points.end(), [](const oracle_point& a, const oracle_point& b) {
        return a.loss < b.loss;
    });
    for (int i = 0; i < k; ++i) {
        for (int j = 0; j < points[i].args.size(); ++j) {
            centroids[i][j] = (double)(points[i].args[j]);
        }
    }

}

void assignClusters(std::vector<oracle_point>& points, const std::vector<std::vector<double>>& centroids) {
    std::set<int> cluster_set;
    for (auto& point : points) {
        double minDist = std::numeric_limits<double>::max();
        int c = -1;
        for (int i = 0; i < centroids.size(); ++i) {
            double dist = euclideanDistanceToCentroid(point, centroids[i]);
            // assert dist is a normal number
            assert(!std::isnan(dist) && !std::isinf(dist) && dist >= 0);
            if (dist < minDist) {
                minDist = dist;
                c = i;
            }
        }
        assert(c >= 0 && c < centroids.size());
        point.cluster = c;
        cluster_set.insert(point.cluster);
    }
    return;
}

void updateCentroids(std::vector<std::vector<double>>& centroids, const std::vector<oracle_point>& points, int k) {
    std::vector<int> counts(k, 0);
    centroids.assign(k, std::vector<double>(points[0].args.size(), 0.0));
    // in case overflow
    std::vector<std::vector<double>> sum(k, std::vector<double>(points[0].args.size(), 0.0));
    for (const auto& point : points) {
        for (int i = 0; i < point.args.size(); ++i) {
            sum[point.cluster][i] += (double)(point.args[i]);
        }
        counts[point.cluster]++;
    }
    for (int i = 0; i < k; ++i) {
        if (counts[i] == 0){
            // FIXME: keep the old centroid as it is
            continue;
        }
        for (int j = 0; j < centroids[i].size(); ++j) {
            assert(counts[i] != 0);
            centroids[i][j] = (uint64_t)(sum[i][j] / counts[i]);
        }
    }
}

bool hasConverged(const std::vector<std::vector<double>>& oldCentroids, const std::vector<std::vector<double>>& newCentroids, double tolerance) {
    for (int i = 0; i < oldCentroids.size(); ++i) {
        if (euclideanDistanceBetweenCentroids(oldCentroids[i], newCentroids[i]) > tolerance) {
            return false;
        }
    }
    return true;
}

void kmeans(std::vector<oracle_point>& points, int k, int maxIterations, double tolerance){
    std::vector<std::vector<double>> centroids(k, std::vector<double>(points[0].args.size(), 0.0));
    initializeCentroids(centroids, points, k);
    for (int iter = 0; iter < maxIterations; ++iter) {
        assignClusters(points, centroids);
        std::vector<std::vector<double>> newCentroids = centroids;
        updateCentroids(newCentroids, points, k);
        if (hasConverged(centroids, newCentroids, tolerance)) {
            break;
        }
        centroids = newCentroids;
    }
    return;
}

std::vector<oracle_point> clustering_select(std::set<oracle_point>& points, int k, int maxIterations, double tolerance){
    // convert set to vector
    std::vector<oracle_point> points_vec(points.begin(), points.end());
    assert(points.size() == points_vec.size());
    if (k >= points.size()){
        return points_vec;
    }
    assert(points_vec.size() > k);
    // clustering
    kmeans(points_vec, k, maxIterations, tolerance);
    // in each cluster, select the point with the lowest loss
    std::vector<oracle_point> ret(k);
    for (int i = 0; i < points_vec.size(); i++){
        assert(points_vec[i].cluster >= 0 && points_vec[i].cluster < k);
        if (ret[points_vec[i].cluster].args.size() == 0 || points_vec[i].loss < ret[points_vec[i].cluster].loss){
            ret[points_vec[i].cluster] = points_vec[i];
        }
    }
    std::vector<oracle_point> pruned_ret;
    for (int i = 0; i < ret.size(); i++) {
        if (ret[i].cluster != -1) {
            pruned_ret.push_back(ret[i]);
        }
    }
    return pruned_ret;
}

std::vector<oracle_point> clustering(std::set<oracle_point>& points, int k, int maxIterations, double tolerance){
    // convert set to vector
    std::vector<oracle_point> points_vec(points.begin(), points.end());
    assert(points.size() == points_vec.size());
    if (k >= points.size()){
        return points_vec;
    }
    assert(points_vec.size() > k);
    // clustering
    kmeans(points_vec, k, maxIterations, tolerance);
    return points_vec;
}