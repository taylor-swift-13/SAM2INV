int main1(){
  int z81, iz, btf, wqz;

  z81=(1%17)+17;
  iz=0;
  btf=0;
  wqz=iz;

  while (1) {
      wqz = wqz + 1;
      btf++;
      wqz--;
      btf = (1)+(btf);
      iz += 1;
      if (iz>=z81) {
          break;
      }
  }

}
