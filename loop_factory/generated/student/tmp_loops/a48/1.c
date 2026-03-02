int main1(int b,int m){
  int r, g, v;

  r=54;
  g=0;
  v=b;

  while (g<r) {
      v = v+4;
      if (g+4<=v+r) {
          v = v%4;
      }
  }

}
