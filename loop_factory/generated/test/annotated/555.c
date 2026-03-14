int main1(int d){
  int ua, yy, bt, mfoz, f44;
  ua=(d%17)+6;
  yy=0;
  bt=ua;
  mfoz=ua;
  f44=yy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bt == mfoz;
  loop invariant (yy == 0) ==> (f44 == 0 && mfoz == ua && bt == ua);
  loop invariant (yy == 0) || (yy == ua);
  loop invariant (f44 >= 0);
  loop invariant ua == ((\at(d,Pre) % 17) + 6);
  loop invariant (mfoz == ua) || (mfoz == ua + 4);
  loop invariant (f44 == 0) || (f44 == ua + 4);
  loop assigns bt, mfoz, f44, yy;
*/
while (1) {
      if (!(yy<ua)) {
          break;
      }
      bt += 4;
      mfoz = (4)+(mfoz);
      f44 += mfoz;
      yy = ua;
  }
}