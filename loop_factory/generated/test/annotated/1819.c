int main1(){
  int h, bs1, h5, mvb;
  h=0;
  bs1=0;
  h5=0;
  mvb=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h5 == bs1;
  loop invariant mvb >= 0;
  loop invariant h5 == 6 - mvb;
  loop invariant (mvb < 6) ==> (h % 4 == 3);
  loop invariant h >= 0;
  loop invariant h5 >= 0;
  loop assigns mvb, h, h5, bs1;
*/
while (mvb>0) {
      mvb -= 1;
      h = h+1*1;
      h5 = h5+1*1;
      bs1 = bs1+1*1;
      h = h*4+3;
  }
}