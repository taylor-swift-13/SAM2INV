int main1(int a,int k){
  int m, u, v;

  m=20;
  u=m;
  v=-1;

  while (u>2) {
      v = v+3;
      v = v+u;
      if (u+7<=k+m) {
          v = v+v;
      }
  }

}
