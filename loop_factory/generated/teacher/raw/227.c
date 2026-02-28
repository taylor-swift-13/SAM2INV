int main1(int m,int q){
  int i, e, o;

  i=(q%17)+16;
  e=0;
  o=-8;

  while (e+2<=i) {
      if (o+1<i) {
          o = o%9;
      }
      e = e+2;
  }

}
