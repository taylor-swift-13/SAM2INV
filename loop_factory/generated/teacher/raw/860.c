int main1(int n,int p){
  int w, y, v, r;

  w=n-10;
  y=0;
  v=4;
  r=y;

  while (v!=0&&r!=0) {
      if (v>r) {
          v = v-r;
      }
      else {
          r = r-v;
      }
  }

}
