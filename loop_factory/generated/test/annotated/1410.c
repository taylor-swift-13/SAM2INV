int main1(int n){
  int bw, w, tx, cpy;
  bw=n;
  w=bw;
  tx=12;
  cpy=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cpy + tx == n + 12;
  loop invariant bw == n;
  loop invariant tx == 12 + 3*w - 3*n;
  loop invariant cpy + 3*w == 4 * \at(n, Pre);
  loop invariant w >= \at(n, Pre);
  loop assigns cpy, tx, w;
*/
while (w-1>=0) {
      cpy = cpy - 3;
      tx = tx + 3;
      w += 1;
  }
}