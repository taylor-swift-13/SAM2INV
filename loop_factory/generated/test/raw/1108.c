int main1(){
  int s24, okcj, ieq, ra, wxz, vpc7, jr, h;

  s24=77;
  okcj=0;
  ieq=1;
  ra=0;
  wxz=0;
  vpc7=-3;
  jr=16;
  h=0;

  while (ieq<=s24) {
      ra = ra+2*ieq-1;
      wxz = wxz + okcj;
      ieq++;
      jr = jr + ra;
      h += 1;
      h = wxz+vpc7+jr;
  }

  while (1) {
      if (!(okcj<=s24)) {
          break;
      }
      jr = jr+okcj*okcj;
      h += 1;
      okcj = okcj + 1;
      vpc7 = (vpc7+s24)+(-(ra));
      h = h + 5;
  }

}
