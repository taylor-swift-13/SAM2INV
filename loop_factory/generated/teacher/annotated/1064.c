int main1(int m,int p){
  int g, v, u, q;

  g=p-1;
  v=0;
  u=0;
  q=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant g == p - 1;
  loop invariant q >= 0;
  loop invariant u % 2 == 0;

  loop invariant g == \at(p, Pre) - 1;


  loop invariant g == \at(p, Pre) - 1 && q >= 0 && (q <= g || g < 0);
  loop invariant m == \at(m, Pre) && p == \at(p, Pre) && u % 2 == 0;
  loop assigns u, q;
*/
while (q<g) {
      u = u+m;
      q = q+1;
      u = u*2;
  }

}
