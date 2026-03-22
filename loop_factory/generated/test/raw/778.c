int main1(int o){
  int u, eq, aa, h, ju4;

  u=(o%36)+8;
  eq=u+2;
  aa=o;
  h=4;
  ju4=-2;

  while (1) {
      if (!(eq>=u+1)) {
          break;
      }
      h = h*h+aa;
      ju4 = ju4*o;
      aa = aa%9;
      eq = eq - 3;
  }

}
