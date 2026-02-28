int main1(int k,int p){
  int l, c, a, u;

  l=57;
  c=0;
  a=0;
  u=l;

  while (c+1<=l) {
      u = l-a;
      a = a+1;
      u = u-1;
      if ((c%9)==0) {
          a = a-c;
      }
      a = a+u;
      if ((c%9)==0) {
          u = u+3;
      }
  }

}
