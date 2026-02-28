int main1(int k,int m,int n,int q){
  int x, u, v;

  x=44;
  u=0;
  v=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant x == 44;
  loop assigns v;
*/
while (1) {
      v = v+4;
      if (v+3<x) {
          v = v+1;
      }
      else {
          v = v+v;
      }
  }

}
