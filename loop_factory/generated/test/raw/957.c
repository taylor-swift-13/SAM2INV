int main1(int c,int d){
  int dlw, hln, l;

  dlw=d+5;
  hln=0;
  l=d;

  while (hln<dlw) {
      l += 2;
      hln++;
      d = d + 3;
      c += hln;
  }

}
