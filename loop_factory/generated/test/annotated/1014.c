int main1(int x){
  int lsb, j79, d, rvc, er, o919;
  lsb=x-7;
  j79=0;
  d=0;
  rvc=0;
  er=0;
  o919=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o919 == 5 + ((j79)/5)*10 + ((j79)%5)*(((j79)%5) - 1)/2;
  loop invariant 0 <= j79;
  loop invariant 0 <= o919;
  loop invariant o919 >= 5;
  loop invariant 0 <= rvc;
  loop invariant rvc <= 4;
  loop invariant 0 <= er;
  loop invariant er <= 4;
  loop invariant lsb == \at(x, Pre) - 7;
  loop invariant o919 == 5 + 10*(j79/5) + ((j79%5)*((j79%5)-1))/2;
  loop assigns d, er, j79, o919, rvc;
*/
while (1) {
      if (!(j79<lsb)) {
          break;
      }
      rvc = j79%5;
      if (!(!(j79>=o919))) {
          er = (j79-o919)%5;
          d = d+rvc-er;
      }
      else {
          d = d + rvc;
      }
      j79 += 1;
      o919 = o919 + rvc;
  }
}