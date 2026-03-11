int main1(){
  int db, dae, cgey;
  db=18;
  dae=db;
  cgey=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*(cgey + 5) == 18 - dae;
  loop invariant -5 <= cgey <= 1;
  loop invariant db == 18;
  loop assigns cgey, dae;
*/
while (dae>2) {
      cgey++;
      dae = dae - 3;
  }
}