int main1(int b,int n){
  int i, w, v;

  i=(b%39)+14;
  w=0;
  v=i;

  while (w<i) {
      v = v+2;
      if ((w%7)==0) {
          v = v+w;
      }
      else {
          v = v-v;
      }
  }

}
