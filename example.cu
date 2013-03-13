/*

reduce0 :: (Scalar a, Num (Exp a))  => FrontStage a ()
reduce0 = do
  l <- Len
  if l==1
    then Return ()
    else do binOpStage (+) id (+(fromIntegral l)`div`2)
            reduce0

reduce1 :: (Scalar a, Num (Exp a))  => FrontStage a ()
reduce1 = do
  l <- Len
  if l==1
    then Return ()
    else do fakeProg $ \ix a -> (a!ix) + (a!(ix + (fromIntegral (len a)`div`2)))
            reduce1

*/

extern "C" __global__ void kernel(int *input0,int *output0);
__global__ void kernel(int *input0,int *output0){

  extern __shared__ __attribute__ ((aligned (16))) unsigned char sbase[];
  ((int *)sbase)[threadIdx.x] = (input0[((blockIdx.x*1024)+threadIdx.x)]+input0[(((blockIdx.x*1024)+threadIdx.x)+1024)]);
  __syncthreads();
  if (threadIdx.x<512){
    ((int *)(sbase + 8192))[threadIdx.x] = (((int *)sbase)[threadIdx.x]+((int *)sbase)[(threadIdx.x+512)]);
    
  }
  __syncthreads();
  if (threadIdx.x<256){
    ((int *)sbase)[threadIdx.x] = (((int *)(sbase+8192))[threadIdx.x]+((int *)(sbase+8192))[(threadIdx.x+256)]);
    
  }
  __syncthreads();
  if (threadIdx.x<128){
    ((int *)(sbase + 2048))[threadIdx.x] = (((int *)sbase)[threadIdx.x]+((int *)sbase)[(threadIdx.x+128)]);
    
  }
  __syncthreads();
  if (threadIdx.x<64){
    ((int *)sbase)[threadIdx.x] = (((int *)(sbase+2048))[threadIdx.x]+((int *)(sbase+2048))[(threadIdx.x+64)]);
    
  }
  __syncthreads();
  if (threadIdx.x<32){
    ((int *)(sbase + 512))[threadIdx.x] = (((int *)sbase)[threadIdx.x]+((int *)sbase)[(threadIdx.x+32)]);
    
  }
  __syncthreads();
  if (threadIdx.x<16){
    ((int *)sbase)[threadIdx.x] = (((int *)(sbase+512))[threadIdx.x]+((int *)(sbase+512))[(threadIdx.x+16)]);
    
  }
  if (threadIdx.x<8){
    ((int *)(sbase + 128))[threadIdx.x] = (((int *)sbase)[threadIdx.x]+((int *)sbase)[(threadIdx.x+8)]);
    
  }
  if (threadIdx.x<4){
    ((int *)sbase)[threadIdx.x] = (((int *)(sbase+128))[threadIdx.x]+((int *)(sbase+128))[(threadIdx.x+4)]);
    
  }
  if (threadIdx.x<2){
    ((int *)(sbase + 32))[threadIdx.x] = (((int *)sbase)[threadIdx.x]+((int *)sbase)[(threadIdx.x+2)]);
    
  }
  if (threadIdx.x<1){
    output0[((blockIdx.x*1024)+threadIdx.x)] = (((int *)(sbase+32))[threadIdx.x]+((int *)(sbase+32))[(threadIdx.x+1)]);
    
  }
  
}


/*

bitonic0 :: (Scalar a, Ord a)  => FrontStage a ()
bitonic0 = do
    l <- Len
    br (l`div`2)
    where br d =
            if d==0
                then return ()
                else do
                    SFMap (\[a,b] -> return [a`op`b]) [ixf,(+de).ixf] [ixf,(+de).ixf]
                        where op a b = [a`mine`b,a`maxe`b]
                    br (d`div`2)
                        where ixf i = i`mod`de+(i`div`de)*2*de
                              de = fromIntegral d

*/

__global__ void kernel(int *input0,int *output0){
  
  extern __shared__ __attribute__ ((aligned (16))) unsigned char sbase[];
  ((int *)sbase)[(threadIdx.x*2)] = min(input0[((((blockIdx.x*1024)+threadIdx.x)%512)+(((((blockIdx.x*1024)+threadIdx.x)/512)*2)*512))],input0[(((((blockIdx.x*1024)+threadIdx.x)%512)+(((((blockIdx.x*1024)+threadIdx.x)/512)*2)*512))+512)]);
  ((int *)sbase)[((threadIdx.x*2)+1)] = max(input0[((((blockIdx.x*1024)+threadIdx.x)%512)+(((((blockIdx.x*1024)+threadIdx.x)/512)*2)*512))],input0[(((((blockIdx.x*1024)+threadIdx.x)%512)+(((((blockIdx.x*1024)+threadIdx.x)/512)*2)*512))+512)]);
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]);
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]);
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]);
  ((int *)sbase)[((threadIdx.x*2)+1)] = max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]);
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]);
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]);
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]);
  ((int *)sbase)[((threadIdx.x*2)+1)] = max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]);
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]);
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]);
  ((int *)sbase)[(threadIdx.x*2)] = min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]);
  ((int *)sbase)[((threadIdx.x*2)+1)] = max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]);
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]);
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]);
  ((int *)sbase)[(threadIdx.x*2)] = min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]);
  ((int *)sbase)[((threadIdx.x*2)+1)] = max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]);
  output0[(((blockIdx.x*1024)+threadIdx.x)*2)] = min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]);
  output0[((((blockIdx.x*1024)+threadIdx.x)*2)+1)] = max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]);
  
}



/*


bitonic0 :: (Scalar a, Ord a) => FrontStage a ()
bitonic0 = bt 1
  where bt :: (Scalar a, Ord a) => Word32 -> FrontStage a ()
        bt e = do l <- Len
                  if e >= l
                    then return ()
                    else do
                        br e e
                        bt (2*e)
        br :: (Scalar a, Ord a) => Word32 -> Word32 -> FrontStage a ()
        br d e =
            if d==0
                then return ()
                else do
                    SFMap op [ixf,(+de).ixf] [ixf,(+de).ixf]
                    br (d`div`2) e
                        where ixf i = i`mod`de+(i`div`de)*2*de
                              de = Literal d
                              ee = Literal e
                              op :: (Scalar a, Ord a) => [Exp a] -> Exp Word32 -> TProgram [Exp a]
                              op [a,b] ix = return [f 0, f 1]
                                where f i = If ((ix`div`ee)`mod`2==*i)
                                                (a`mine`b)
                                                (a`maxe`b)


*/


extern "C" __global__ void kernel(int *input0,int *output0);
__global__ void kernel(int *input0,int *output0){
  
  extern __shared__ __attribute__ ((aligned (16))) unsigned char sbase[];
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/1)%2)==0) ? min(input0[((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))],input0[(((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))+1)]) : max(input0[((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))],input0[(((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))+1)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/1)%2)==1) ? min(input0[((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))],input0[(((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))+1)]) : max(input0[((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))],input0[(((((blockIdx.x*1024)+threadIdx.x)%1)+((((blockIdx.x*1024)+threadIdx.x)/1)*2))+1)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/2)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/2)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/2)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/2)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/4)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/4)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/4)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/4)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/4)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/4)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/8)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/16)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/32)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/64)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/128)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/256)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))+512)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))+512)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))+512)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%512)+(((threadIdx.x/512)*2)*512))+512)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%256)+(((threadIdx.x/256)*2)*256))+256)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%128)+(((threadIdx.x/128)*2)*128))+128)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%64)+(((threadIdx.x/64)*2)*64))+64)]));
  __syncthreads();
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%32)+(((threadIdx.x/32)*2)*32))+32)]));
  __syncthreads();
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%16)+(((threadIdx.x/16)*2)*16))+16)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%8)+(((threadIdx.x/8)*2)*8))+8)]));
  ((int *)sbase)[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)sbase)[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%4)+(((threadIdx.x/4)*2)*4))+4)]));
  ((int *)(sbase + 8192))[(threadIdx.x*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  ((int *)(sbase + 8192))[((threadIdx.x*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]) : max(((int *)sbase)[((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))],((int *)sbase)[(((((blockIdx.x*1024)+threadIdx.x)%2)+(((threadIdx.x/2)*2)*2))+2)]));
  output0[(((blockIdx.x*1024)+threadIdx.x)*2)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==0) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  output0[((((blockIdx.x*1024)+threadIdx.x)*2)+1)] = ((((((blockIdx.x*1024)+threadIdx.x)/512)%2)==1) ? min(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]) : max(((int *)(sbase+8192))[((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))],((int *)(sbase+8192))[(((((blockIdx.x*1024)+threadIdx.x)%1)+((threadIdx.x/1)*2))+1)]));
  
}

