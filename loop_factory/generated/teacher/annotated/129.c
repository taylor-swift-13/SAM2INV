int main1(int m){
  int u, x, v, s;

  u=36;
  x=0;
  v=u;
  s=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant u == 36;
  loop invariant v <= u;
  loop invariant v >= 36;
  loop assigns v;
*/
while (v<u) {
      if (v<u) {
          v = v+1;
      }
  }

}
