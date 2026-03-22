int main1(int p,int x){
  int wx, u4y1, r, gh, q1c, sw5, t9, em;

  wx=p+25;
  u4y1=0;
  r=1;
  gh=1;
  q1c=1;
  sw5=1;
  t9=2;
  em=x;

  while (1) {
      if (!(q1c<=wx)) {
          break;
      }
      r = r*(p/q1c);
      if ((q1c/2)%2==0) {
          sw5 = 1;
      }
      else {
          sw5 = -1;
      }
      gh = gh+sw5*r;
      q1c = q1c + 1;
      r = r*(p/q1c);
      if ((u4y1%4)==0) {
          t9 = t9*t9+x;
      }
      em = em + q1c;
      t9 += em;
      em += p;
      p = p + 5;
  }

}
