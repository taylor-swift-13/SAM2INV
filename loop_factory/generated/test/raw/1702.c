int main1(int n){
  int v, c, bb, g;

  v=n;
  c=0;
  bb=0;
  g=0;

  while (c < v) {
      g = (g + 1) % 3;
      bb = bb + 3;
      c = c + 1;
      n = n + c;
  }

}
