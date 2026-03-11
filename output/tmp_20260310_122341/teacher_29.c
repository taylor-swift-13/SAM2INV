int main1(int n,int q){
  int j, v, u;

  j=73;
  v=0;
  u=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= v && v <= j;
  loop invariant u == v + 6;
  loop invariant j == 73;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant u - v == 6;
  loop invariant v >= 0;
  loop invariant v <= j;
  loop assigns v, u;
*/
while (v<j) {
      if (v+2<=v+j) {
          u = u+1;
      }
      else {
          u = u+1;
      }
      v = v+1;
  }

}
