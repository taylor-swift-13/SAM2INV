int main1(int p){
  int c6v, w, om, a7g;

  c6v=p;
  w=0;
  om=c6v;
  a7g=4;

  while (w<=c6v-1) {
      a7g = a7g+om*w;
      w = c6v;
  }

  while (1) {
      if (!(om<=a7g-1)) {
          break;
      }
      om++;
      w += p;
  }

}
