int main1(){
  int oer7, fk, a2xt;
  oer7=1*5;
  fk=0;
  a2xt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a2xt <= oer7;
  loop invariant ((a2xt == 0) ==> (fk == 0)) &&
    (((a2xt != 0) && (a2xt % 3 == 0)) ==> (fk == 6)) &&
    ((a2xt % 3 == 1) ==> (fk == 2)) &&
    ((a2xt % 3 == 2) ==> (fk == 4));
  loop invariant 0 <= a2xt;
  loop invariant (fk % 6) == ((2 * a2xt) % 6);
  loop invariant 0 <= fk;
  loop invariant fk <= 6;
  loop invariant oer7 == 5;
  loop assigns a2xt, fk;
*/
while (a2xt<oer7) {
      fk = (fk+1)%6;
      a2xt += 1;
      fk += 1;
  }
}