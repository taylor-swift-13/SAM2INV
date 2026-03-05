int main40(int z,int h,int v){
  int cz, wq, f, ln, ilm5;

  cz=176;
  wq=cz;
  f=v;
  ln=cz;
  ilm5=cz;

  for (; wq>0; wq = wq/2) {
      f += ln;
      ln = ln + ilm5;
      ilm5 += 4;
  }

}
