int main1(){
  int kyi, qjnx;
  kyi=51;
  qjnx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qjnx <= kyi;
  loop invariant qjnx % 3 == 0;
  loop invariant qjnx >= 0;
  loop invariant kyi == 51;
  loop assigns qjnx;
*/
while (qjnx<kyi) {
      qjnx += 2;
      qjnx += 1;
  }
}