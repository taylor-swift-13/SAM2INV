int main1(int k,int q){
  int u, o, n, v;

  u=q+23;
  o=u;
  n=q;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o <= u;
  loop invariant u == \at(q, Pre) + 23;
  loop invariant q == \at(q, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant u == q + 23;
  loop invariant u == \at(q, Pre) + 23 &&
                   o <= u &&
                   o >= \at(q, Pre) + 23 &&
                   n >= \at(q, Pre) &&
                   q == \at(q, Pre);
  loop invariant o >= q;
  loop assigns n, o;
*/
while (1) {
      if (o>=u) {
          break;
      }
      n = n+3;
      o = o+1;
      n = n*2+4;
  }

}
