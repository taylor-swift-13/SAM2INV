int main11(int r,int d){
  int t9, he3t, dic, j5hg, ri, l8, xj;

  t9=(d%12)+19;
  he3t=1;
  dic=0;
  j5hg=r;
  ri=25;
  l8=0;
  xj=-5;

  while (he3t<=t9-1) {
      dic++;
      he3t = 2*he3t;
      j5hg = j5hg + 1;
      l8 = l8*3+(he3t%3)+1;
      xj++;
      ri += j5hg;
  }

}
