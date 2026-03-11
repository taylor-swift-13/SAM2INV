int main1(int u,int j){
  int eex, id, cts, v2;
  eex=u+10;
  id=eex;
  cts=-3;
  v2=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eex == \at(u,Pre) + 10;
  loop invariant id == eex;
  loop invariant 2*(j - \at(j,Pre)) == (cts + 3) * id;
  loop invariant ( (cts == -3 && v2 == u) || (v2 + cts == eex + 2) );
  loop assigns j, cts, v2;
*/
while (cts<eex) {
      v2 = eex-cts;
      j = j + id;
      cts += 2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop assigns cts, u, v2;
*/
while (v2<eex) {
      cts = (eex)+(-(v2));
      u = u + id;
      v2 = v2 + 1;
  }
/*@
  assert !(v2<eex) &&
         (eex == \at(u,Pre) + 10);
*/

}