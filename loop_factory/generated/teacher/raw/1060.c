int main1(int b,int q){
  int e, v, w, u;

  e=(b%33)+17;
  v=1;
  w=0;
  u=v;

  while (w<e) {
      if (w>=e/2) {
          u = u+2;
      }
      w = w+1;
      u = u+u;
  }

}
