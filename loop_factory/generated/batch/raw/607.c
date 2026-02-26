int main1(int a,int m){
  int l, u, v;

  l=(a%9)+17;
  u=1;
  v=a;

  while (u<=l/3) {
      v = v+4;
      v = v+v;
  }

}
