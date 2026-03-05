int main1(int t,int q){
  int tl, ah;
  tl=71;
  ah=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ah >= 0;
  loop invariant ah <= 2*tl + 1;
  loop invariant q >= \at(q, Pre);
  loop invariant t == \at(t, Pre);
  loop invariant tl == 71;
  loop assigns ah, q;
*/
while (ah<=tl) {
      ah = 2*ah;
      ah = ah + 1;
      q += tl;
  }
}