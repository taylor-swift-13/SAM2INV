int main1(int p){
  int yk4, ked, ap, uj;
  yk4=9;
  ked=0;
  ap=0;
  uj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ap == ked * p);
  loop invariant (2 * uj == p * ked * (ked + 1));
  loop invariant 0 <= ked <= yk4;
  loop assigns ap, ked, uj;
*/
while (ked < yk4) {
      ap += p;
      ked += 1;
      uj = uj + ap;
  }
}