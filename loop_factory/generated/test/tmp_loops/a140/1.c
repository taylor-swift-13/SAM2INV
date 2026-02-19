int main1(int b,int q){
  int l, i, v, u;

  l=q;
  i=0;
  v=q;
  u=-2;

  while (i<l) {
      v = v+u+u;
      v = v+1;
      i = i+1;
  }

  while (u<l) {
      v = v+2;
      v = v+1;
      u = u+1;
  }

}
