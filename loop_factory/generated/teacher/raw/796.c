int main1(int a,int m){
  int h, w, v;

  h=m;
  w=0;
  v=a;

  while (1) {
      v = v+3;
      if ((w%7)==0) {
          v = v+w;
      }
      else {
          v = v+v;
      }
  }

}
