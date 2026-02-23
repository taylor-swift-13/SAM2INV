int main1(int k,int m){
  int e, y, v;

  e=k+24;
  y=0;
  v=e;

  while (y<e) {
      v = v-v;
      if (y+1<=v+e) {
          v = v+1;
      }
      y = y+1;
  }

}
