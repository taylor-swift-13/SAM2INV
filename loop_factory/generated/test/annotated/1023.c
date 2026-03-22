int main1(int d,int x){
  int t3, x9e, v9id, u7m, j9;
  t3=d;
  x9e=t3;
  v9id=0;
  u7m=-1;
  j9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j9 == (\at(d, Pre) - x9e) * v9id;
  loop invariant u7m == -1 + v9id * (((\at(d, Pre) - x9e) * ((\at(d, Pre) - x9e) - 1)) / 2);
  loop invariant j9 == v9id * (d - x9e);
  loop invariant u7m == -1 + v9id * (((d - x9e) * (d - x9e - 1)) / 2);
  loop invariant x9e <= d;
  loop assigns j9, u7m, x9e;
*/
while (x9e-1>=0) {
      u7m = u7m + j9;
      j9 += v9id;
      x9e = x9e - 1;
  }
}