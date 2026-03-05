int main1(int w){
  int u, wu, n8;

  u=54;
  wu=0;
  n8=0;

  for (; wu<u; wu += 1) {
      n8++;
      if (n8>=2) {
          n8 -= 2;
          n8++;
      }
  }

}
