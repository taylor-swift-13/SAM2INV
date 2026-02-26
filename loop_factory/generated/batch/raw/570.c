int main1(int m,int q){
  int y, o, v;

  y=22;
  o=0;
  v=o;

  while (1) {
      if (v+2<y) {
          v = v+o;
      }
      else {
          v = v-v;
      }
      v = v+1;
      o = o+1;
  }

}
