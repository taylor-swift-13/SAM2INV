int main1(int a,int b,int k,int n){
  int l, i, v;

  l=(a%20)+19;
  i=1;
  v=i;

  while (i<l) {
      v = v+v;
      v = v*v;
      i = i*3;
  }

}
