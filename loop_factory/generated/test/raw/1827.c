int main1(int u){
  int ax, rt4, ad4k, l, ya3;

  ax=(u%34)+15;
  rt4=2;
  ad4k=0;
  l=0;
  ya3=0;

  while (rt4 < ax) {
      ad4k = ad4k + rt4 * rt4;
      ya3 = (rt4 * u)+(ya3);
      l = l+ad4k+ya3;
      u += 2;
      rt4 = ax;
  }

}
