int main1(int a,int b,int m,int p){
  int l, i, v;

  l=(a%33)+15;
  i=0;
  v=a;

  while (i<l) {
      v = v*2;
      v = v%7;
      i = i+1;
  }

}
