int main1(int p,int q){
  int s, m, u, v;

  s=p;
  m=0;
  u=s;
  v=s;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre) && q == \at(q, Pre) && s == \at(p, Pre);

  loop invariant s == \at(p, Pre) && q == \at(q, Pre) && u >= \at(p, Pre) && v <= \at(p, Pre) && (m==0 || u % 3 == 0);
  loop invariant s == p;
  loop invariant p == \at(p, Pre);
  loop invariant m >= 0;
  loop invariant s >= 0 ==> m <= s;
  loop invariant s >= 0 ==> v >= 0;
  loop invariant m == 0 || u % 3 == 0;
  loop invariant s == \at(p, Pre) && q == \at(q, Pre);
  loop invariant u * v <= \at(p, Pre) * \at(p, Pre);
  loop invariant s == \at(p, Pre);

  loop invariant (m==0 && u == \at(p, Pre) && v == \at(p, Pre)) || (m>0 && u % 3 == 0);
  loop invariant (m == 0 ==> u == s && v == s);
  loop invariant (m == 0) || (u % 3 == 0);
  loop invariant s == \at(p, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

  loop invariant s == \at(p, Pre) && m >= 0 && (\at(p, Pre) >= 0 ==> m <= s);
  loop invariant (\at(p, Pre) >= 0 ==> v >= 0 && u >= 0);
  loop assigns u, v, m;
*/
while (m+1<=s) {
      u = u*3;
      v = v/3;
      m = m+1;
  }
/*@
  assert !(m+1<=s) &&
         (p == \at(p, Pre) && q == \at(q, Pre) && s == \at(p, Pre));
*/


}
