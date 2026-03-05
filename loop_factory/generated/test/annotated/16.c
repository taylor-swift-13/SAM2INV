int main1(int u){
  int rjo, rdl;
  rjo=0;
  rdl=-19728;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rjo == 0;
  loop invariant u == \at(u, Pre);
  loop invariant rdl <= -19728;
  loop assigns rdl, u;
*/
while (rdl<=-8) {
      rdl = rdl+rdl-2;
      rdl = rdl + 3;
      u = u + rjo;
  }
}