int main1(int p){
  int bk, kg2, ed, w;
  bk=p+6;
  kg2=0;
  ed=0;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ed == 0;
  loop invariant bk == p + 6;
  loop invariant (kg2 == 0) || (kg2 == bk);
  loop invariant (kg2 == 0) ==> (ed == 0 && w == 0);
  loop invariant 0 <= w;
  loop assigns ed, w, kg2;
*/
while (kg2 < bk) {
      ed = kg2*(kg2-1)*(2*kg2-1)/6;
      w = w*3+(ed%6)+3;
      kg2 = bk;
  }
}