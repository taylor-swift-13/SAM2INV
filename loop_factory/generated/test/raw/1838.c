int main1(){
  int uv, pfw, ug, hl, vn4;

  uv=1;
  pfw=0;
  ug=uv;
  hl=uv;
  vn4=ug * ug;

  while (pfw < uv) {
      pfw = pfw + 1;
      vn4++;
      ug = ug + pfw;
      hl = hl*hl;
  }

}
