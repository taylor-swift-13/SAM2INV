int main1(){
  int wvf, c2x, awu4;
  wvf=57;
  c2x=wvf;
  awu4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wvf == 57;
  loop invariant awu4 >= 0;
  loop invariant c2x == 57 - 6*awu4;
  loop assigns awu4, c2x;
*/
while (c2x>5) {
      awu4++;
      c2x -= 6;
  }
}