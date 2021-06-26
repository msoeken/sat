pub fn waerden(j: usize, k: usize, n: usize) -> Vec<Vec<i32>> {
    let mut clauses = Vec::new();

    for d in 1..=(n / (j - 1)) {
        for i in 1..=(n - (j - 1) * d) {
            clauses.push((0..j).map(|jj| (i + jj * d) as i32).collect());
        }
    }

    for d in 1..=(n / (k - 1)) {
        for i in 1..=(n - (k - 1) * d) {
            clauses.push((0..k).map(|kk| -((i + kk * d) as i32)).collect());
        }
    }

    clauses
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn waerden339() {
        for clause in waerden(3, 3, 8) {
            println!("{:?}", clause);
        }
    }
}
