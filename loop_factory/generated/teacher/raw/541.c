int main1(int n,int q){
  int w, k, v;

  w=45;
  k=0;
  v=k;

  while (k<=w-1) {
      if (v<w+2) {
          v = v+v;
      }
      else {
          v = v-v;
      }
      k = k+1;
  }

}
