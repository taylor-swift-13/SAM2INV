int main1(){
  int zeo, b9f, mhg;
  zeo=(1%17)+9;
  b9f=0;
  mhg=b9f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b9f == 0;
  loop invariant zeo == 10;
  loop invariant mhg >= 0;
  loop invariant mhg % 8 == 0;
  loop assigns mhg;
*/
while (b9f+4<=zeo) {
      mhg += 4;
      mhg += mhg;
  }
}