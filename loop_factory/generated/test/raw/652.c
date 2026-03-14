int main1(int i,int e){
  int ofi, t8i3, g5v, a68r, k7;

  ofi=(i%7)+16;
  t8i3=0;
  g5v=0;
  a68r=1;
  k7=0;

  while (t8i3<=ofi-1) {
      g5v++;
      a68r += g5v;
      t8i3 = ofi;
  }

  while (t8i3<g5v) {
      k7 = g5v-t8i3;
      i += k7;
      t8i3++;
  }

}
