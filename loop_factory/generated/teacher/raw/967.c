int main1(int b,int k){
  int r, u, w;

  r=b-4;
  u=0;
  w=5;

  while (u+1<=r) {
      if (u+7<=k+r) {
          w = w+u;
      }
      w = w+1;
      u = u+1;
  }

}
