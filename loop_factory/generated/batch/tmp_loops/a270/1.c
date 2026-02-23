int main1(int a,int m){
  int r, h, v;

  r=(m%38)+18;
  h=0;
  v=m;

  while (h<r) {
      v = v*v+v;
      h = h+1;
  }

}
