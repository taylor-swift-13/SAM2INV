int main1(int b){
  int owm6, rar, xb, odw, xd;
  owm6=b+16;
  rar=-1;
  xb=20;
  odw=1;
  xd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant odw == 1 + xd;
  loop invariant rar == xd - 1;
  loop invariant 0 <= xb;
  loop invariant xb <= 20;
  loop invariant 0 <= xd;
  loop invariant ((xd*(xd+1) <= 40) ==> xb == 20 - (xd*(xd+1))/2);
  loop invariant owm6 == \at(b, Pre) + 16;
  loop invariant b == \at(b, Pre);
  loop invariant ((xd*(xd+1))/2 <= 20) ==> (xb == 20 - (xd*(xd+1))/2);
  loop assigns xb, odw, xd, rar;
*/
while (xb>0&&odw<=owm6) {
      if (xb>odw) {
          xb -= odw;
      }
      else {
          xb = 0;
      }
      xd++;
      odw = odw + 1;
      rar++;
  }
}