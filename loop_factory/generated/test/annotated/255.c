int main1(int v,int d){
  int plv, svx7, m6q;
  plv=45;
  svx7=0;
  m6q=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m6q == 2 + 2*svx7;
  loop invariant svx7 <= plv;
  loop invariant d == \at(d, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant 0 <= svx7;
  loop invariant plv == 45;
  loop assigns m6q, svx7;
*/
while (svx7<plv) {
      m6q += 2;
      svx7 = svx7 + 1;
  }
}