int main1(int c){
  int vo, pwx5, te, uh9p, cq8, mlt, o0;

  vo=0;
  pwx5=(c%20)+10;
  te=(c%15)+8;
  uh9p=-5;
  cq8=c;
  mlt=2;
  o0=c;

  while (pwx5>0&&te>0) {
      if (vo%2==0) {
          pwx5 = pwx5 - 1;
      }
      else {
          te -= 1;
      }
      vo++;
      if ((vo%7)==0) {
          c = c + o0;
      }
      uh9p = uh9p + te;
      mlt += pwx5;
      uh9p = uh9p + 1;
      cq8 += uh9p;
      mlt = mlt + c;
  }

}
