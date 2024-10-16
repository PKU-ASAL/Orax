#ifndef CLUSTERING_H
#define CLUSTERING_H
#include <iostream>
#include <vector>
#include <cmath>
#include <limits>
#include <cstdlib>
#include <ctime>
#include "seed_pool.h"
#include "assert.h"

std::vector<oracle_point> clustering_select(std::set<oracle_point>& points, int k, int maxIterations = 5, double tolerance = 1e-4);

std::vector<oracle_point> clustering(std::set<oracle_point>& points, int k, int maxIterations = 5, double tolerance = 1e-4);

#endif