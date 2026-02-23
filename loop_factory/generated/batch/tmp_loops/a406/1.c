int main1(int k,int p){
  int u, i, v, l;

  u=k;
  i=0;
  v=i;
  l=8;

  while (v!=0&&l!=0) {
      if (v>l) {
          v = v-l;
      }
      else {
          l = l-v;
      }
      v = v+l+l;
      v = v+1;
  }

}
