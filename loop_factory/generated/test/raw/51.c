int main1(){
  int ub, xyu, nju, p, a;

  ub=1+13;
  xyu=ub;
  nju=0;
  p=0;
  a=6;

  while (nju<ub&&a>0) {
      p = p + a;
      nju = nju + 1;
      p += xyu;
      a -= 1;
  }

}
