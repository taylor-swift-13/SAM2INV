int main1(){
  int o4r, eco, bkh, qsp3, kd7, os;
  o4r=1;
  eco=1;
  bkh=4;
  qsp3=eco;
  kd7=o4r;
  os=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kd7 == qsp3;
  loop invariant os <= 9;
  loop invariant os >= 0;
  loop invariant bkh % 4 == 0;
  loop assigns kd7, bkh, qsp3, os;
*/
while (os>0) {
      kd7 = kd7+os*os;
      bkh = bkh+qsp3*qsp3;
      qsp3 = qsp3+os*os;
      os -= 1;
      bkh = bkh*4;
  }
}